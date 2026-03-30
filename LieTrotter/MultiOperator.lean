/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multi-Operator Lie-Trotter Product Formula

Generalization of the two-operator Lie-Trotter formula to a list of operators:
  `(∏ᵢ exp(Aᵢ/n))^n → exp(∑ᵢ Aᵢ)` as `n → ∞`.
-/

import LieTrotter.Assembly

open Filter Topology NormedSpace
open scoped BigOperators

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-!
## Auxiliary: Norm bound for List.sum

`‖l.sum‖ ≤ (l.map norm).sum` for a list in a seminormed group.
-/

omit [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸] in
lemma norm_list_sum_le (l : List 𝔸) : ‖l.sum‖ ≤ (l.map (fun a => ‖a‖)).sum := by
  induction l with
  | nil => simp [norm_zero]
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    calc ‖a + rest.sum‖ ≤ ‖a‖ + ‖rest.sum‖ := norm_add_le _ _
      _ ≤ ‖a‖ + (rest.map (fun a => ‖a‖)).sum := by linarith

/-!
## Auxiliary: Product of norms bound via List.prod_le_prod'

For bounding `‖P‖` where `P` is a product of exponentials.
-/

omit [NormedAlgebra 𝕂 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private lemma list_sum_map_div (As : List 𝔸) (n : ℝ) :
    (As.map (fun A => ‖A‖ / n)).sum = (As.map (fun A => ‖A‖)).sum / n := by
  induction As with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]; ring

omit [CompleteSpace 𝔸] in
include 𝕂 in
private lemma list_norm_prod_exp_smul_le (As : List 𝔸) (n : ℕ) (hn : 0 < n) :
    ‖(As.map (fun A => exp ((n : 𝕂)⁻¹ • A))).prod‖ ≤
      Real.exp ((As.map (fun A => ‖A‖)).sum / n) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have norm_inv_n : ‖(n : 𝕂)⁻¹‖ = ((n : ℝ))⁻¹ := by
    rw [norm_inv, RCLike.norm_natCast]
  induction As with
  | nil =>
    simp [norm_one, Real.exp_zero]
  | cons a rest ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    calc ‖exp ((n : 𝕂)⁻¹ • a) * (rest.map (fun A => exp ((n : 𝕂)⁻¹ • A))).prod‖
        ≤ ‖exp ((n : 𝕂)⁻¹ • a)‖ *
          ‖(rest.map (fun A => exp ((n : 𝕂)⁻¹ • A))).prod‖ := norm_mul_le _ _
      _ ≤ Real.exp (‖a‖ / n) *
          Real.exp ((rest.map (fun A => ‖A‖)).sum / n) := by
          apply mul_le_mul
          · calc ‖exp ((n : 𝕂)⁻¹ • a)‖
                ≤ Real.exp ‖(n : 𝕂)⁻¹ • a‖ := norm_exp_le (𝕂 := 𝕂) _
              _ ≤ Real.exp (‖(n : 𝕂)⁻¹‖ * ‖a‖) := by
                  gcongr; exact norm_smul_le _ _
              _ = Real.exp (‖a‖ / n) := by rw [norm_inv_n, inv_mul_eq_div]
          · exact ih
          · positivity
          · positivity
      _ = Real.exp ((‖a‖ + (rest.map (fun A => ‖A‖)).sum) / n) := by
          rw [← Real.exp_add, add_div]

/-!
## Lemma 1: Multi-operator step error

`‖(as.map exp).prod - exp(as.sum)‖ ≤ (as.map norm).sum ^ 2 * exp((as.map norm).sum)`

By induction on the list `as`.
-/

include 𝕂 in
theorem norm_list_prod_exp_sub_exp_sum (as : List 𝔸) :
    ‖(as.map (fun a => exp a)).prod - exp as.sum‖ ≤
      (as.map (fun a => ‖a‖)).sum ^ 2 * Real.exp ((as.map (fun a => ‖a‖)).sum) := by
  induction as with
  | nil =>
    simp [exp_zero]
  | cons a rest ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    set P := (rest.map (fun a => exp a)).prod with hP_def
    set S := rest.sum with hS_def
    have split : exp a * P - exp (a + S) =
        exp a * (P - exp S) + (exp a * exp S - exp (a + S)) := by noncomm_ring
    rw [split]
    set T := (rest.map (fun a => ‖a‖)).sum with hT_def
    have hT : 0 ≤ T := by
      apply List.sum_nonneg; intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨b, _, rfl⟩ := hx
      exact norm_nonneg b
    have hS_le : ‖S‖ ≤ T := norm_list_sum_le rest
    -- Term 1: ‖exp(a) * (P - exp S)‖ ≤ exp(‖a‖) * T² * exp(T)
    have h_term1 : ‖exp a * (P - exp S)‖ ≤
        Real.exp ‖a‖ * (T ^ 2 * Real.exp T) := by
      calc ‖exp a * (P - exp S)‖
          ≤ ‖exp a‖ * ‖P - exp S‖ := norm_mul_le _ _
        _ ≤ Real.exp ‖a‖ * ‖P - exp S‖ := by
            gcongr; exact norm_exp_le (𝕂 := 𝕂) a
        _ ≤ Real.exp ‖a‖ * (T ^ 2 * Real.exp T) := by
            gcongr
    -- Term 2: ‖exp(a) * exp(S) - exp(a+S)‖ ≤ 2‖a‖*T*exp(‖a‖+T)
    have h_term2 : ‖exp a * exp S - exp (a + S)‖ ≤
        2 * ‖a‖ * T * Real.exp (‖a‖ + T) := by
      calc ‖exp a * exp S - exp (a + S)‖
          ≤ 2 * ‖a‖ * ‖S‖ * Real.exp (‖a‖ + ‖S‖) :=
            norm_exp_mul_exp_sub_exp_add' (𝕂 := 𝕂) a S
        _ ≤ 2 * ‖a‖ * T * Real.exp (‖a‖ + T) := by
            gcongr
    -- Combine
    calc ‖exp a * (P - exp S) + (exp a * exp S - exp (a + S))‖
        ≤ ‖exp a * (P - exp S)‖ + ‖exp a * exp S - exp (a + S)‖ := norm_add_le _ _
      _ ≤ Real.exp ‖a‖ * (T ^ 2 * Real.exp T) +
          2 * ‖a‖ * T * Real.exp (‖a‖ + T) := add_le_add h_term1 h_term2
      _ ≤ (‖a‖ + T) ^ 2 * Real.exp (‖a‖ + T) := by
          set s := ‖a‖
          have hs : 0 ≤ s := norm_nonneg a
          rw [Real.exp_add]
          have hE : 0 < Real.exp s * Real.exp T := by positivity
          have key : T ^ 2 + 2 * s * T ≤ (s + T) ^ 2 := by nlinarith [sq_nonneg s]
          nlinarith [mul_le_mul_of_nonneg_left key hE.le]

/-!
## Lemma 2: Specialized step error for scaled operators

Apply Lemma 1 with `aᵢ = n⁻¹ • Aᵢ`.
-/

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private lemma list_sum_map_smul (As : List 𝔸) (c : 𝕂) :
    (As.map (fun A => c • A)).sum = c • As.sum := by
  induction As with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, smul_add]

omit [NormOneClass 𝔸] [CompleteSpace 𝔸] in
private lemma list_sum_map_norm_smul (As : List 𝔸) (n : ℕ)
    (norm_inv_n : ‖(n : 𝕂)⁻¹‖ = ((n : ℝ))⁻¹) :
    ((As.map (fun A => (n : 𝕂)⁻¹ • A)).map (fun a => ‖a‖)).sum =
      (As.map (fun A => ‖A‖)).sum / n := by
  induction As with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, norm_smul, norm_inv_n]; ring

include 𝕂 in
theorem norm_list_prod_exp_smul_sub_exp_smul_sum (As : List 𝔸) (n : ℕ) (hn : 0 < n) :
    ‖(As.map (fun A => exp ((n : 𝕂)⁻¹ • A))).prod -
      exp ((n : 𝕂)⁻¹ • As.sum)‖ ≤
      ((As.map (fun A => ‖A‖)).sum / n) ^ 2 *
        Real.exp ((As.map (fun A => ‖A‖)).sum / n) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have norm_inv_n : ‖(n : 𝕂)⁻¹‖ = ((n : ℝ))⁻¹ := by
    rw [norm_inv, RCLike.norm_natCast]
  -- Key identities to connect to Lemma 1
  have h_map_eq : As.map (fun A => exp ((n : 𝕂)⁻¹ • A)) =
      (As.map (fun A => (n : 𝕂)⁻¹ • A)).map (fun a => exp a) := by
    simp [List.map_map]
  have h_sum : (As.map (fun A => (n : 𝕂)⁻¹ • A)).sum = (n : 𝕂)⁻¹ • As.sum :=
    list_sum_map_smul As _
  rw [h_map_eq, ← h_sum]
  -- Apply Lemma 1
  have h1 := norm_list_prod_exp_sub_exp_sum (𝕂 := 𝕂) (As.map (fun A => (n : 𝕂)⁻¹ • A))
  -- Simplify norms
  have h_norms := list_sum_map_norm_smul (𝕂 := 𝕂) As n norm_inv_n
  rw [h_norms] at h1
  exact h1

/-!
## Lemma 3: Convergence rate for multi-operator formula

5-step assembly, same pattern as `lie_trotter_error_rate`.
-/

include 𝕂 in
theorem lie_trotter_list_error_rate (As : List 𝔸) :
    ∃ C > 0, ∀ n : ℕ, 0 < n →
      ‖((As.map (fun A => exp ((n : 𝕂)⁻¹ • A))).prod) ^ n -
       exp As.sum‖ ≤ C / n := by
  set S := (As.map (fun A => ‖A‖)).sum with hS_def
  refine ⟨S ^ 2 * Real.exp S + 1, by positivity, ?_⟩
  intro n hn
  -- Step 1: Rewrite exp(As.sum) = exp(As.sum/n)^n
  have hpow : exp As.sum = (exp ((n : 𝕂)⁻¹ • As.sum)) ^ n :=
    (exp_div_pow As.sum n hn).symm
  rw [hpow]
  set P := (As.map (fun A => exp ((n : 𝕂)⁻¹ • A))).prod with hP_def
  set Q := exp ((n : 𝕂)⁻¹ • As.sum) with hQ_def
  -- Step 2: Apply telescoping norm bound
  have h_telesc := norm_pow_sub_pow_le' P Q n
  -- Step 3: Bound ‖P - Q‖ by step error
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h_step : ‖P - Q‖ ≤ (S / n) ^ 2 * Real.exp (S / n) := by
    rw [hP_def, hQ_def]
    exact norm_list_prod_exp_smul_sub_exp_smul_sum (𝕂 := 𝕂) As n hn
  -- Step 4: Bound max(‖P‖, ‖Q‖)
  have norm_inv_n : ‖(n : 𝕂)⁻¹‖ = ((n : ℝ))⁻¹ := by
    rw [norm_inv, RCLike.norm_natCast]
  have h_max : max ‖P‖ ‖Q‖ ≤ Real.exp (S / n) := by
    have h_P : ‖P‖ ≤ Real.exp (S / n) := by
      rw [hP_def]
      exact list_norm_prod_exp_smul_le (𝕂 := 𝕂) As n hn
    have h_Q : ‖Q‖ ≤ Real.exp (S / n) := by
      calc ‖Q‖ = ‖exp ((n : 𝕂)⁻¹ • As.sum)‖ := rfl
        _ ≤ Real.exp ‖(n : 𝕂)⁻¹ • As.sum‖ := norm_exp_le (𝕂 := 𝕂) _
        _ ≤ Real.exp (‖(n : 𝕂)⁻¹‖ * ‖As.sum‖) := by
            gcongr; exact norm_smul_le _ _
        _ ≤ Real.exp (S / n) := by
            gcongr
            rw [norm_inv_n, inv_mul_eq_div]
            exact div_le_div_of_nonneg_right (norm_list_sum_le As) hn_pos.le
    exact max_le h_P h_Q
  -- Step 5: Combine and simplify
  calc ‖P ^ n - Q ^ n‖
      ≤ n * ‖P - Q‖ * (max ‖P‖ ‖Q‖) ^ (n - 1) := h_telesc
    _ ≤ n * ((S / n) ^ 2 * Real.exp (S / n)) *
        (Real.exp (S / n)) ^ (n - 1) := by
        gcongr
    _ ≤ (S ^ 2 * Real.exp S + 1) / n := by
        have h_pow : Real.exp (S / ↑n) * Real.exp (S / ↑n) ^ (n - 1) =
            Real.exp (S / ↑n) ^ n := by
          cases n with
          | zero => omega
          | succ m => simp [pow_succ']
        have h_exp_pow : Real.exp (S / ↑n) ^ n = Real.exp S := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
        have h_lhs : ↑n * ((S / ↑n) ^ 2 * Real.exp (S / ↑n)) *
            Real.exp (S / ↑n) ^ (n - 1) =
            S ^ 2 * Real.exp S / ↑n := by
          have : ↑n * ((S / ↑n) ^ 2 * Real.exp (S / ↑n)) *
              Real.exp (S / ↑n) ^ (n - 1) =
              ↑n * (S / ↑n) ^ 2 *
              (Real.exp (S / ↑n) * Real.exp (S / ↑n) ^ (n - 1)) := by ring
          rw [this, h_pow, h_exp_pow]; field_simp
        rw [h_lhs]
        exact (div_le_div_iff_of_pos_right hn_pos).mpr (le_add_of_nonneg_right zero_le_one)

/-!
## Theorem 4: Main theorem -- the multi-operator Lie-Trotter formula
-/

include 𝕂 in
/-- **The Multi-Operator Lie-Trotter Product Formula.**
    For any list of elements `As` in a complete normed algebra,
    `(∏ᵢ exp(Aᵢ/n))^n → exp(∑ᵢ Aᵢ)` as `n → ∞`. -/
theorem lie_trotter_list (As : List 𝔸) :
    Filter.Tendsto
      (fun n : ℕ => ((As.map (fun A => exp ((n : 𝕂)⁻¹ • A))).prod) ^ n)
      atTop (nhds (exp As.sum)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨C, hC_pos, hC_bound⟩ := lie_trotter_list_error_rate (𝕂 := 𝕂) As
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  refine ⟨N + 1, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hn_pos : 0 < n := by omega
  calc ‖((As.map (fun A => exp ((↑n : 𝕂)⁻¹ • A))).prod) ^ n - exp As.sum‖
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
