/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strang Splitting (Symmetric Lie-Trotter)

The symmetric Lie-Trotter formula:
  `(exp(A/(2n)) exp(B/n) exp(A/(2n)))^n → exp(A+B)` as `n → ∞`

with O(1/n) convergence rate.
-/

import LieTrotter.Assembly

open Filter Topology NormedSpace
open scoped BigOperators

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Step 1: Symmetric step error bound

`‖exp(a) exp(b) exp(a) - exp(a+b+a)‖ ≤ 2‖a‖(‖a‖+2‖b‖) exp(2‖a‖+‖b‖)`

Split algebraically:
  `exp(a)exp(b)exp(a) - exp(a+b+a)`
    `= exp(a) * (exp(b)exp(a) - exp(b+a)) + (exp(a)exp(b+a) - exp(a+(b+a)))`
-/

include 𝕂 in
theorem norm_exp_mul_exp_mul_exp_sub_exp_add (a b : 𝔸) :
    ‖exp a * exp b * exp a - exp (a + b + a)‖ ≤
      2 * ‖a‖ * (‖a‖ + 2 * ‖b‖) * Real.exp (2 * ‖a‖ + ‖b‖) := by
  -- Algebraic splitting
  have alg : exp a * exp b * exp a - exp (a + b + a) =
      exp a * (exp b * exp a - exp (b + a)) +
      (exp a * exp (b + a) - exp (a + (b + a))) := by noncomm_ring
  rw [alg]
  -- Triangle inequality
  calc ‖exp a * (exp b * exp a - exp (b + a)) +
        (exp a * exp (b + a) - exp (a + (b + a)))‖
      ≤ ‖exp a * (exp b * exp a - exp (b + a))‖ +
        ‖exp a * exp (b + a) - exp (a + (b + a))‖ := norm_add_le _ _
    _ ≤ ‖exp a‖ * ‖exp b * exp a - exp (b + a)‖ +
        ‖exp a * exp (b + a) - exp (a + (b + a))‖ := by
        gcongr; exact norm_mul_le _ _
    _ ≤ Real.exp ‖a‖ * (2 * ‖b‖ * ‖a‖ * Real.exp (‖b‖ + ‖a‖)) +
        (2 * ‖a‖ * ‖b + a‖ * Real.exp (‖a‖ + ‖b + a‖)) := by
        gcongr
        · exact norm_exp_le (𝕂 := 𝕂) a
        · exact norm_exp_mul_exp_sub_exp_add' (𝕂 := 𝕂) b a
        · exact norm_exp_mul_exp_sub_exp_add' (𝕂 := 𝕂) a (b + a)
    _ ≤ Real.exp ‖a‖ * (2 * ‖b‖ * ‖a‖ * Real.exp (‖b‖ + ‖a‖)) +
        (2 * ‖a‖ * (‖b‖ + ‖a‖) * Real.exp (‖a‖ + (‖b‖ + ‖a‖))) := by
        gcongr
        · exact norm_add_le b a
        · exact norm_add_le b a
    _ ≤ 2 * ‖a‖ * (‖a‖ + 2 * ‖b‖) * Real.exp (2 * ‖a‖ + ‖b‖) := by
        -- Simplify the exponents
        have hexp1 : Real.exp ‖a‖ * Real.exp (‖b‖ + ‖a‖) = Real.exp (2 * ‖a‖ + ‖b‖) := by
          rw [← Real.exp_add]; congr 1; ring
        have hexp2 : Real.exp (‖a‖ + (‖b‖ + ‖a‖)) = Real.exp (2 * ‖a‖ + ‖b‖) := by
          congr 1; ring
        -- Rearrange Term 1: exp(‖a‖) * (2‖b‖‖a‖ * exp(‖b‖+‖a‖)) = 2‖a‖‖b‖ * exp(2‖a‖+‖b‖)
        have h1 : Real.exp ‖a‖ * (2 * ‖b‖ * ‖a‖ * Real.exp (‖b‖ + ‖a‖)) =
            2 * ‖a‖ * ‖b‖ * Real.exp (2 * ‖a‖ + ‖b‖) := by
          have : Real.exp ‖a‖ * (2 * ‖b‖ * ‖a‖ * Real.exp (‖b‖ + ‖a‖)) =
              2 * ‖a‖ * ‖b‖ * (Real.exp ‖a‖ * Real.exp (‖b‖ + ‖a‖)) := by ring
          rw [this, hexp1]
        -- Rearrange Term 2
        have h2 : 2 * ‖a‖ * (‖b‖ + ‖a‖) * Real.exp (‖a‖ + (‖b‖ + ‖a‖)) =
            2 * ‖a‖ * (‖a‖ + ‖b‖) * Real.exp (2 * ‖a‖ + ‖b‖) := by
          rw [hexp2]; ring
        rw [h1, h2]
        -- Now: 2‖a‖‖b‖ * E + 2‖a‖(‖a‖+‖b‖) * E ≤ 2‖a‖(‖a‖+2‖b‖) * E
        -- This is equality since ‖b‖ + (‖a‖+‖b‖) = ‖a‖+2‖b‖
        nlinarith [Real.exp_pos (2 * ‖a‖ + ‖b‖), norm_nonneg a, norm_nonneg b]

/-!
## Step 2: Scalar identity

`(2n)⁻¹ • A + n⁻¹ • B + (2n)⁻¹ • A = n⁻¹ • (A + B)`
-/

omit [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸] in
include 𝕂 in
private lemma half_inv_add_half_inv (n : ℕ) (hn : 0 < n) :
    (2 * (n : 𝕂))⁻¹ + (2 * (n : 𝕂))⁻¹ = (n : 𝕂)⁻¹ := by
  have hn_ne : (n : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2n_ne : (2 : 𝕂) * (n : 𝕂) ≠ 0 := mul_ne_zero two_ne_zero hn_ne
  field_simp; norm_num

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
include 𝕂 in
private lemma symmetric_smul_eq (A B : 𝔸) (n : ℕ) (hn : 0 < n) :
    (2 * (n : 𝕂))⁻¹ • A + (n : 𝕂)⁻¹ • B + (2 * (n : 𝕂))⁻¹ • A =
      (n : 𝕂)⁻¹ • (A + B) := by
  have h : (2 * (n : 𝕂))⁻¹ • A + (2 * (n : 𝕂))⁻¹ • A = (n : 𝕂)⁻¹ • A := by
    rw [← add_smul, half_inv_add_half_inv (𝕂 := 𝕂) n hn]
  rw [smul_add]
  have : (2 * (n : 𝕂))⁻¹ • A + (n : 𝕂)⁻¹ • B + (2 * (n : 𝕂))⁻¹ • A =
      ((2 * (n : 𝕂))⁻¹ • A + (2 * (n : 𝕂))⁻¹ • A) + (n : 𝕂)⁻¹ • B := by abel
  rw [this, h]

/-!
## Step 3: Symmetric step error specialized to A/(2n), B/n

`‖exp(A/(2n)) exp(B/n) exp(A/(2n)) - exp((A+B)/n)‖ ≤ C/n²`

The general bound gives `2‖a‖(‖a‖+2‖b‖) exp(2‖a‖+‖b‖)` with `‖a‖=‖A‖/(2n)`, `‖b‖=‖B‖/n`.
This simplifies to `‖A‖(‖A‖+4‖B‖)/(2n²) exp((‖A‖+‖B‖)/n)`.
-/

include 𝕂 in
private theorem strang_step_error (A B : 𝔸) (n : ℕ) (hn : 0 < n) :
    ‖exp ((2 * (n : 𝕂))⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B) *
      exp ((2 * (n : 𝕂))⁻¹ • A) - exp ((n : 𝕂)⁻¹ • (A + B))‖ ≤
      ‖A‖ * (‖A‖ + 4 * ‖B‖) / (2 * (n : ℝ) ^ 2) *
        Real.exp ((‖A‖ + ‖B‖) / n) := by
  -- Rewrite the exp target using scalar identity
  have hsmul : (2 * (n : 𝕂))⁻¹ • A + (n : 𝕂)⁻¹ • B + (2 * (n : 𝕂))⁻¹ • A =
      (n : 𝕂)⁻¹ • (A + B) := symmetric_smul_eq (𝕂 := 𝕂) A B n hn
  rw [← hsmul]
  -- Apply the general bound
  set a := (2 * (n : 𝕂))⁻¹ • A
  set b := (n : 𝕂)⁻¹ • B
  have h_gen := norm_exp_mul_exp_mul_exp_sub_exp_add (𝕂 := 𝕂) a b
  -- Compute norms
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h2n_pos : (0 : ℝ) < 2 * (n : ℝ) := by linarith
  have h2n_ne : (2 : 𝕂) * (n : 𝕂) ≠ 0 :=
    mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (by omega))
  have hn_ne : (n : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have norm_inv_2n : ‖(2 * (n : 𝕂))⁻¹‖ = (2 * (n : ℝ))⁻¹ := by
    rw [norm_inv, norm_mul, RCLike.norm_ofNat, RCLike.norm_natCast]
  have norm_inv_n : ‖(n : 𝕂)⁻¹‖ = ((n : ℝ))⁻¹ := by
    rw [norm_inv, RCLike.norm_natCast]
  have norm_a : ‖a‖ = ‖A‖ / (2 * n) := by
    show ‖(2 * (n : 𝕂))⁻¹ • A‖ = _
    rw [norm_smul, norm_inv_2n, div_eq_inv_mul]
  have norm_b : ‖b‖ = ‖B‖ / n := by
    show ‖(n : 𝕂)⁻¹ • B‖ = _
    rw [norm_smul, norm_inv_n, div_eq_inv_mul]
  rw [norm_a, norm_b] at h_gen
  -- Simplify the RHS of h_gen to match our target
  calc ‖exp a * exp b * exp a - exp (a + b + a)‖
      ≤ 2 * (‖A‖ / (2 * ↑n)) * (‖A‖ / (2 * ↑n) + 2 * (‖B‖ / ↑n)) *
        Real.exp (2 * (‖A‖ / (2 * ↑n)) + ‖B‖ / ↑n) := h_gen
    _ = ‖A‖ * (‖A‖ + 4 * ‖B‖) / (2 * (↑n) ^ 2) *
        Real.exp ((‖A‖ + ‖B‖) / ↑n) := by
      field_simp; ring

/-!
## Step 4: Convergence rate
-/

include 𝕂 in
theorem strang_error_rate (A B : 𝔸) :
    ∃ C > 0, ∀ n : ℕ, 0 < n →
      ‖(exp ((2 * (n : 𝕂))⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B) *
        exp ((2 * (n : 𝕂))⁻¹ • A)) ^ n - exp (A + B)‖ ≤ C / n := by
  refine ⟨‖A‖ * (‖A‖ + 4 * ‖B‖) / 2 * Real.exp (‖A‖ + ‖B‖) + 1,
    by positivity, ?_⟩
  intro n hn
  -- Step 1: Rewrite exp(A+B) = exp((A+B)/n)^n
  have hpow : exp (A + B) = (exp ((n : 𝕂)⁻¹ • (A + B))) ^ n :=
    (exp_div_pow (𝕂 := 𝕂) (A + B) n hn).symm
  rw [hpow]
  set S := exp ((2 * (n : 𝕂))⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B) *
    exp ((2 * (n : 𝕂))⁻¹ • A) with hS_def
  set Q := exp ((n : 𝕂)⁻¹ • (A + B)) with hQ_def
  -- Step 2: Apply telescoping
  have h_telesc := norm_pow_sub_pow_le' S Q n
  -- Step 3: Bound ‖S - Q‖
  have h_step : ‖S - Q‖ ≤ ‖A‖ * (‖A‖ + 4 * ‖B‖) / (2 * (n : ℝ) ^ 2) *
      Real.exp ((‖A‖ + ‖B‖) / n) := by
    rw [hS_def, hQ_def]
    exact strang_step_error (𝕂 := 𝕂) A B n hn
  -- Step 4: Bound max(‖S‖, ‖Q‖)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h2n_pos : (0 : ℝ) < 2 * (n : ℝ) := by linarith
  have norm_inv_2n : ‖(2 * (n : 𝕂))⁻¹‖ = (2 * (n : ℝ))⁻¹ := by
    rw [norm_inv, norm_mul, RCLike.norm_ofNat, RCLike.norm_natCast]
  have norm_inv_n : ‖(n : 𝕂)⁻¹‖ = ((n : ℝ))⁻¹ := by
    rw [norm_inv, RCLike.norm_natCast]
  have h_max : max ‖S‖ ‖Q‖ ≤ Real.exp ((‖A‖ + ‖B‖) / n) := by
    have norm_half_A : ‖(2 * (n : 𝕂))⁻¹ • A‖ = ‖A‖ / (2 * n) := by
      rw [norm_smul, norm_inv_2n, div_eq_inv_mul]
    have norm_inv_B : ‖(n : 𝕂)⁻¹ • B‖ = ‖B‖ / n := by
      rw [norm_smul, norm_inv_n, div_eq_inv_mul]
    have h_S : ‖S‖ ≤ Real.exp ((‖A‖ + ‖B‖) / n) := by
      calc ‖S‖ = ‖exp ((2 * (n : 𝕂))⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B) *
              exp ((2 * (n : 𝕂))⁻¹ • A)‖ := rfl
        _ ≤ ‖exp ((2 * (n : 𝕂))⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B)‖ *
            ‖exp ((2 * (n : 𝕂))⁻¹ • A)‖ := norm_mul_le _ _
        _ ≤ (‖exp ((2 * (n : 𝕂))⁻¹ • A)‖ * ‖exp ((n : 𝕂)⁻¹ • B)‖) *
            ‖exp ((2 * (n : 𝕂))⁻¹ • A)‖ := by
            gcongr; exact norm_mul_le _ _
        _ ≤ (Real.exp ‖(2 * (n : 𝕂))⁻¹ • A‖ * Real.exp ‖(n : 𝕂)⁻¹ • B‖) *
            Real.exp ‖(2 * (n : 𝕂))⁻¹ • A‖ := by
            gcongr
            · exact norm_exp_le (𝕂 := 𝕂) _
            · exact norm_exp_le (𝕂 := 𝕂) _
            · exact norm_exp_le (𝕂 := 𝕂) _
        _ = Real.exp (‖(2 * (n : 𝕂))⁻¹ • A‖ + ‖(n : 𝕂)⁻¹ • B‖ +
            ‖(2 * (n : 𝕂))⁻¹ • A‖) := by
            rw [Real.exp_add, Real.exp_add]
        _ = Real.exp (‖A‖ / (2 * ↑n) + ‖B‖ / ↑n + ‖A‖ / (2 * ↑n)) := by
            rw [norm_half_A, norm_inv_B]
        _ = Real.exp ((‖A‖ + ‖B‖) / n) := by
            congr 1; field_simp; ring
    have h_Q : ‖Q‖ ≤ Real.exp ((‖A‖ + ‖B‖) / n) := by
      calc ‖Q‖ = ‖exp ((n : 𝕂)⁻¹ • (A + B))‖ := rfl
        _ ≤ Real.exp ‖(n : 𝕂)⁻¹ • (A + B)‖ := norm_exp_le (𝕂 := 𝕂) _
        _ ≤ Real.exp (‖(n : 𝕂)⁻¹‖ * ‖A + B‖) := by
            gcongr; exact norm_smul_le _ _
        _ ≤ Real.exp (‖(n : 𝕂)⁻¹‖ * (‖A‖ + ‖B‖)) := by
            gcongr; exact norm_add_le A B
        _ = Real.exp ((‖A‖ + ‖B‖) / n) := by
            rw [norm_inv_n, inv_mul_eq_div]
    exact max_le h_S h_Q
  -- Step 5: Combine and simplify
  calc ‖S ^ n - Q ^ n‖
      ≤ n * ‖S - Q‖ * (max ‖S‖ ‖Q‖) ^ (n - 1) := h_telesc
    _ ≤ n * (‖A‖ * (‖A‖ + 4 * ‖B‖) / (2 * (n : ℝ) ^ 2) *
        Real.exp ((‖A‖ + ‖B‖) / n)) *
        (Real.exp ((‖A‖ + ‖B‖) / n)) ^ (n - 1) := by
        gcongr
    _ ≤ (‖A‖ * (‖A‖ + 4 * ‖B‖) / 2 * Real.exp (‖A‖ + ‖B‖) + 1) / n := by
        set s := ‖A‖ + ‖B‖
        set c := ‖A‖ * (‖A‖ + 4 * ‖B‖)
        have h_pow : Real.exp (s / ↑n) * Real.exp (s / ↑n) ^ (n - 1) =
            Real.exp (s / ↑n) ^ n := by
          cases n with
          | zero => omega
          | succ m => simp [pow_succ']
        have h_exp_pow : Real.exp (s / ↑n) ^ n = Real.exp s := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
        have h_lhs : ↑n * (c / (2 * (↑n) ^ 2) * Real.exp (s / ↑n)) *
            Real.exp (s / ↑n) ^ (n - 1) =
            c / 2 * Real.exp s / ↑n := by
          have : ↑n * (c / (2 * (↑n) ^ 2) * Real.exp (s / ↑n)) *
              Real.exp (s / ↑n) ^ (n - 1) =
              ↑n * (c / (2 * (↑n) ^ 2)) *
              (Real.exp (s / ↑n) * Real.exp (s / ↑n) ^ (n - 1)) := by ring
          rw [this, h_pow, h_exp_pow]; field_simp
        rw [h_lhs]
        exact (div_le_div_iff_of_pos_right hn_pos).mpr (le_add_of_nonneg_right zero_le_one)

/-!
## Step 5: Main theorem
-/

/-- **The Symmetric Lie-Trotter (Strang Splitting) Product Formula.**
    For any elements `A, B` in a complete normed algebra,
    `(exp(A/(2n)) exp(B/n) exp(A/(2n)))^n → exp(A+B)` as `n → ∞`. -/
theorem symmetric_lie_trotter (A B : 𝔸) :
    Filter.Tendsto
      (fun n : ℕ => (exp ((2 * (n : 𝕂))⁻¹ • A) * exp ((n : 𝕂)⁻¹ • B) *
                      exp ((2 * (n : 𝕂))⁻¹ • A)) ^ n)
      atTop (nhds (exp (A + B))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨C, hC_pos, hC_bound⟩ := strang_error_rate (𝕂 := 𝕂) A B
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  refine ⟨N + 1, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hn_pos : 0 < n := by omega
  calc ‖(exp ((2 * (↑n : 𝕂))⁻¹ • A) * exp ((↑n : 𝕂)⁻¹ • B) *
        exp ((2 * (↑n : 𝕂))⁻¹ • A)) ^ n - exp (A + B)‖
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
